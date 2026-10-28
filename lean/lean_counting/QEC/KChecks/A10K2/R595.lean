import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2380 = true := by
  decide +kernel

theorem tot2380 : totK PA10K2 A10K2.t2380 = [0, 0, 438071677347, 1746245691482, 2013452268504, 588901279455, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows2381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2381 = true := by
  decide +kernel

theorem tot2381 : totK PA10K2 A10K2.t2381 = [0, 0, 31314613976, 800800439944, 2105151460044, 1492405159464, 317738394950, 24969229125, 0, 0] := by
  decide +kernel

theorem rows2382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2382 = true := by
  decide +kernel

theorem tot2382 : totK PA10K2 A10K2.t2382 = [0, 0, 238785603865, 1115246188842, 1881646884881, 1122690066843, 190104791325, 6034215561, 0, 0] := by
  decide +kernel

theorem rows2383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2383 = true := by
  decide +kernel

theorem tot2383 : totK PA10K2 A10K2.t2383 = [0, 0, 581706818495, 1905622924402, 1729181133506, 469610578718, 31806683705, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
