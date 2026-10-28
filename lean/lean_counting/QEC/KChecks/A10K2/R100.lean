import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t400 = true := by
  decide +kernel

theorem tot400 : totK PA10K2 A10K2.t400 = [257786448200, 1475586081220, 2090946378928, 812098438172, 60959423803, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t401 = true := by
  decide +kernel

theorem tot401 : totK PA10K2 A10K2.t401 = [297783531355, 1191962744981, 1867379392629, 1161543061871, 214404696947, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t402 = true := by
  decide +kernel

theorem tot402 : totK PA10K2 A10K2.t402 = [395296435550, 1684549779970, 2200901231300, 852422092082, 66084170480, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t403 = true := by
  decide +kernel

theorem tot403 : totK PA10K2 A10K2.t403 = [0, 634541140921, 2169134281848, 1962640487965, 376872026512, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
