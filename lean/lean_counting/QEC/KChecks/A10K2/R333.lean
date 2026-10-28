import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1332 = true := by
  decide +kernel

theorem tot1332 : totK PA10K2 A10K2.t1332 = [0, 0, 0, 447299428909, 1740252252421, 1942611886019, 619944056600, 42531436804, 0, 0] := by
  decide +kernel

theorem rows1333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1333 = true := by
  decide +kernel

theorem tot1333 : totK PA10K2 A10K2.t1333 = [0, 0, 0, 515586040523, 1919211496365, 1928575908625, 443583348270, 18093411651, 0, 0] := by
  decide +kernel

theorem rows1334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1334 = true := by
  decide +kernel

theorem tot1334 : totK PA10K2 A10K2.t1334 = [0, 0, 115325325322, 652023601708, 1762561442774, 1888547508272, 644525235327, 42549660646, 0, 0] := by
  decide +kernel

theorem rows1335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1335 = true := by
  decide +kernel

theorem tot1335 : totK PA10K2 A10K2.t1335 = [0, 0, 478253204978, 1871703306603, 2087303579105, 638754960240, 33364819402, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
