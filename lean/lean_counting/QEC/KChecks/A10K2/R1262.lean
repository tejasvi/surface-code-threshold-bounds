import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5048 = true := by
  decide +kernel

theorem tot5048 : totK PA10K2 A10K2.t5048 = [0, 0, 0, 1073724705136, 2434582990124, 1032984368466, 71239518531, 0, 0, 0] := by
  decide +kernel

theorem rows5049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5049 = true := by
  decide +kernel

theorem tot5049 : totK PA10K2 A10K2.t5049 = [0, 0, 494232055333, 1619251047477, 1803577905836, 835301238188, 147846456327, 5546304973, 0, 0] := by
  decide +kernel

theorem rows5050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5050 = true := by
  decide +kernel

theorem tot5050 : totK PA10K2 A10K2.t5050 = [0, 304661711030, 1189483107107, 1749581078550, 1265517035300, 410918338326, 29791859037, 0, 0, 0] := by
  decide +kernel

theorem rows5051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5051 = true := by
  decide +kernel

theorem tot5051 : totK PA10K2 A10K2.t5051 = [0, 474114351285, 1779426288566, 1962310178474, 610434633776, 40659824465, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
