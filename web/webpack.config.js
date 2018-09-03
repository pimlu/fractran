const path = require('path');
module.exports = {
  entry: {
    main: './src/main.js'
  },
  mode: 'development',
  devtool: 'source-map',
  devServer: {
    contentBase: './dist'
  },
  module: {
    rules: [
      {
        test: /\.js$/,
        exclude: /node_modules/,
        use: {
          loader: "babel-loader"
        }
      },
      {
        test: /\.pegjs$/,
        use: {
          loader: 'pegjs-loader?allowedStartRules[]=ProgInput,allowedStartRules[]=ProgFracs'
        }
      }
    ]
  },
  output: {
      filename: '[name].bundle.js',
      path: path.resolve(__dirname, 'dist')
  },
};