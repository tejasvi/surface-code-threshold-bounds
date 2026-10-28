import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1360 = true := by
  decide +kernel

theorem tot1360 : totK PA10K2 A10K2.t1360 = [0, 0, 299321869460, 1222812534690, 1818346904062, 1100464957812, 202642460066, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1361 = true := by
  decide +kernel

theorem tot1361 : totK PA10K2 A10K2.t1361 = [0, 0, 478122903716, 1839245466465, 2103791569290, 590985309763, 16324656051, 0, 0, 0] := by
  decide +kernel

theorem rows1362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1362 = true := by
  decide +kernel

theorem tot1362 : totK PA10K2 A10K2.t1362 = [0, 0, 0, 607173604735, 2118881257670, 1976725207447, 370714923923, 6853348008, 0, 0] := by
  decide +kernel

theorem rows1363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1363 = true := by
  decide +kernel

theorem tot1363 : totK PA10K2 A10K2.t1363 = [0, 0, 0, 486670839456, 1756198519212, 1924425075539, 660117705356, 50759906737, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
