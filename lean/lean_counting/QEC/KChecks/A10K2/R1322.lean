import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5288 = true := by
  decide +kernel

theorem tot5288 : totK PA10K2 A10K2.t5288 = [0, 0, 442168293250, 1766236273447, 1981750185915, 559849122470, 32470943963, 0, 0, 0] := by
  decide +kernel

theorem rows5289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5289 = true := by
  decide +kernel

theorem tot5289 : totK PA10K2 A10K2.t5289 = [0, 0, 526778248158, 1829453468901, 1872656600607, 458342460148, 31607162994, 0, 0, 0] := by
  decide +kernel

theorem rows5290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5290 = true := by
  decide +kernel

theorem tot5290 : totK PA10K2 A10K2.t5290 = [0, 0, 306467343696, 1500470870886, 2068293024709, 737601858243, 57778438788, 0, 0, 0] := by
  decide +kernel

theorem rows5291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5291 = true := by
  decide +kernel

theorem tot5291 : totK PA10K2 A10K2.t5291 = [0, 0, 213371739588, 1030754773781, 1932375208377, 1211392871528, 233528391130, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
