import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7316 = true := by
  decide +kernel

theorem tot7316 : totK PA10K2 A10K2.t7316 = [0, 0, 0, 1011269942553, 2420323970644, 1115967061497, 77429379986, 0, 0, 0] := by
  decide +kernel

theorem rows7317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7317 = true := by
  decide +kernel

theorem tot7317 : totK PA10K2 A10K2.t7317 = [0, 0, 0, 469506863734, 1805990282322, 1959911609804, 506709063966, 31987755669, 0, 0] := by
  decide +kernel

theorem rows7318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7318 = true := by
  decide +kernel

theorem tot7318 : totK PA10K2 A10K2.t7318 = [0, 0, 0, 559296247192, 1923365005922, 1907475936146, 406289246575, 13149912228, 0, 0] := by
  decide +kernel

theorem rows7319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7319 = true := by
  decide +kernel

theorem tot7319 : totK PA10K2 A10K2.t7319 = [0, 0, 0, 464264388272, 1852018337552, 1931885176914, 439907429019, 31088438951, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
