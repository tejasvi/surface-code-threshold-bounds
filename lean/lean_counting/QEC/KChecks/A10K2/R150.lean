import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t600 = true := by
  decide +kernel

theorem tot600 : totK PA10K2 A10K2.t600 = [0, 0, 510825214428, 1808363924500, 2125387069449, 691076710292, 40858060673, 0, 0, 0] := by
  decide +kernel

theorem rows601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t601 = true := by
  decide +kernel

theorem tot601 : totK PA10K2 A10K2.t601 = [0, 0, 461920259241, 1895443204364, 1929316013346, 445201571034, 25667075836, 0, 0, 0] := by
  decide +kernel

theorem rows602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t602 = true := by
  decide +kernel

theorem tot602 : totK PA10K2 A10K2.t602 = [0, 0, 274454697932, 1356615097493, 2177828429847, 990832178016, 98601352668, 0, 0, 0] := by
  decide +kernel

theorem rows603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t603 = true := by
  decide +kernel

theorem tot603 : totK PA10K2 A10K2.t603 = [0, 0, 42030787920, 585214249905, 1802321767245, 1659760583979, 456260854217, 30650496230, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
