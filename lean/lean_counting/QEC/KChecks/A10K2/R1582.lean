import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6328 = true := by
  decide +kernel

theorem tot6328 : totK PA10K2 A10K2.t6328 = [0, 251986720587, 1160459861120, 1806517119330, 1114707149156, 304472121585, 31276155898, 0, 0, 0] := by
  decide +kernel

theorem rows6329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6329 = true := by
  decide +kernel

theorem tot6329 : totK PA10K2 A10K2.t6329 = [0, 578650951092, 1753813511537, 1669117615683, 663854070289, 121210527949, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows6330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6330 = true := by
  decide +kernel

theorem tot6330 : totK PA10K2 A10K2.t6330 = [0, 219385222726, 1459738544946, 2329301040454, 920961336112, 68484376467, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6331 = true := by
  decide +kernel

theorem tot6331 : totK PA10K2 A10K2.t6331 = [0, 0, 486876088794, 1783529514966, 1917500751075, 513496587724, 31768748853, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
