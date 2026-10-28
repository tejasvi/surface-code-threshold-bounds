import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6368 = true := by
  decide +kernel

theorem tot6368 : totK PA10K2 A10K2.t6368 = [306750524226, 1516127856165, 2115883871922, 755047776224, 44556629621, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6369 = true := by
  decide +kernel

theorem tot6369 : totK PA10K2 A10K2.t6369 = [0, 689172901280, 2128554357610, 1581383305137, 269700699866, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6370 = true := by
  decide +kernel

theorem tot6370 : totK PA10K2 A10K2.t6370 = [0, 497929162183, 1812992279872, 1928408657736, 543404433522, 31987876949, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6371 = true := by
  decide +kernel

theorem tot6371 : totK PA10K2 A10K2.t6371 = [0, 514875442709, 1925303731292, 1861965806017, 456595909321, 26116334861, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
