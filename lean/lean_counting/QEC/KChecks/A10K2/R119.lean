import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t476 = true := by
  decide +kernel

theorem tot476 : totK PA10K2 A10K2.t476 = [0, 521615141752, 1997876770144, 2065278243055, 538370845142, 18784338999, 0, 0, 0, 0] := by
  decide +kernel

theorem rows477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t477 = true := by
  decide +kernel

theorem tot477 : totK PA10K2 A10K2.t477 = [0, 580094462653, 1793775794187, 1798731945104, 628028654209, 63691948969, 0, 0, 0, 0] := by
  decide +kernel

theorem rows478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t478 = true := by
  decide +kernel

theorem tot478 : totK PA10K2 A10K2.t478 = [0, 260006046817, 1547393315222, 2171619354022, 818875865686, 61866981726, 0, 0, 0, 0] := by
  decide +kernel

theorem rows479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t479 = true := by
  decide +kernel

theorem tot479 : totK PA10K2 A10K2.t479 = [0, 0, 524211049680, 1824644704098, 1779043654762, 477040429113, 31082886609, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
