import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1056 = true := by
  decide +kernel

theorem tot1056 : totK PA10K2 A10K2.t1056 = [0, 0, 173806078642, 1119508608237, 2095045217647, 1325105306705, 212738828955, 6281495166, 0, 0] := by
  decide +kernel

theorem rows1057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1057 = true := by
  decide +kernel

theorem tot1057 : totK PA10K2 A10K2.t1057 = [0, 0, 0, 609121793218, 2076714729136, 1937115927792, 412101263951, 12813073358, 0, 0] := by
  decide +kernel

theorem rows1058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1058 = true := by
  decide +kernel

theorem tot1058 : totK PA10K2 A10K2.t1058 = [0, 415295505255, 1410394498101, 1399462651175, 611308251327, 627641045416, 376689991107, 43287591117, 0, 0] := by
  decide +kernel

theorem rows1059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1059 = true := by
  decide +kernel

theorem tot1059 : totK PA10K2 A10K2.t1059 = [0, 395405154995, 1700187506933, 2056700939242, 729606021330, 57003121271, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
