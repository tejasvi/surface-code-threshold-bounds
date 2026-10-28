import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1448 = true := by
  decide +kernel

theorem tot1448 : totK PA10K2 A10K2.t1448 = [0, 0, 0, 583442077426, 2051942583135, 1756632954130, 348452611707, 11318342500, 0, 0] := by
  decide +kernel

theorem rows1449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1449 = true := by
  decide +kernel

theorem tot1449 : totK PA10K2 A10K2.t1449 = [0, 0, 0, 0, 961128220788, 2432809639146, 1120789766833, 71457160460, 0, 0] := by
  decide +kernel

theorem rows1450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1450 = true := by
  decide +kernel

theorem tot1450 : totK PA10K2 A10K2.t1450 = [0, 0, 579756899725, 1868564127781, 1673645076449, 413374163432, 157378898360, 69316020384, 6121173289, 0] := by
  decide +kernel

theorem rows1451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1451 = true := by
  decide +kernel

theorem tot1451 : totK PA10K2 A10K2.t1451 = [0, 0, 182377239714, 1201060936871, 2195651777141, 1150092478234, 133144160663, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
