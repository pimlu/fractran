const path = require('path');
module.exports = {
  entry: {
    main: './src/main.js',
  },
  mode: 'development',
  devtool: 'source-map',
  devServer: {
    contentBase: './dist'
  },
  node: {
    fs: 'empty'
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
      },
      {
        test: /\.wasm$/,
        type: "javascript/auto",
        loader: "file-loader",
      },
      {
        test: /\.worker\.js$/,
        use: { loader: 'worker-loader' }
      }
    ]
  },
  output: {
      filename: '[name].bundle.js',
      path: path.resolve(__dirname, 'dist'),
      globalObject: 'this'
  },
};
