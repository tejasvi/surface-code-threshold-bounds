import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4344 = true := by
  decide +kernel

theorem tot4344 : totK PA10K2 A10K2.t4344 = [0, 0, 469339957255, 1789153075921, 1936939436427, 552196644593, 35974349027, 0, 0, 0] := by
  decide +kernel

theorem rows4345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4345 = true := by
  decide +kernel

theorem tot4345 : totK PA10K2 A10K2.t4345 = [0, 0, 277959440667, 1218388538656, 1946032549604, 1064189319769, 139929600929, 5656154743, 0, 0] := by
  decide +kernel

theorem rows4346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4346 = true := by
  decide +kernel

theorem tot4346 : totK PA10K2 A10K2.t4346 = [0, 0, 509037370054, 1826660284533, 1821173298359, 437786018314, 16735867423, 0, 0, 0] := by
  decide +kernel

theorem rows4347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4347 = true := by
  decide +kernel

theorem tot4347 : totK PA10K2 A10K2.t4347 = [0, 0, 0, 950369951277, 2413069403784, 1117943533444, 77429379986, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
