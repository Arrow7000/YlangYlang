module Errors



/// The errors that can accrue at each stage of the pipeline - so that we can return a unified result from the pipeline that can contain the errors of each stage
type Errors =
    | LexingError of Lexer.LexingErrors
    | ParsingError of ExpressionParsing.ParserError list
    | CanonicalisationError of Lexer.Identifier list
    | TypeError of TypedSyntaxTree.TypeError
