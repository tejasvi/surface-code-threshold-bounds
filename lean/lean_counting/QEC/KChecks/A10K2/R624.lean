import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2496 = true := by
  decide +kernel

theorem tot2496 : totK PA10K2 A10K2.t2496 = [0, 163761173604, 1011248063329, 1946609804293, 1315827472558, 216568885598, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows2497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2497 = true := by
  decide +kernel

theorem tot2497 : totK PA10K2 A10K2.t2497 = [0, 578600964295, 1851967492728, 1800202820791, 517127204063, 31936107789, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2498 = true := by
  decide +kernel

theorem tot2498 : totK PA10K2 A10K2.t2498 = [0, 0, 1060120081549, 2385874415772, 1069862562343, 77355190755, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2499 = true := by
  decide +kernel

theorem tot2499 : totK PA10K2 A10K2.t2499 = [0, 399120657157, 1462785816627, 1895464196663, 983343832987, 167839301729, 6121173289, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
