import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1964 = true := by
  decide +kernel

theorem tot1964 : totK PD2M8K2 D2M8K2.t1964 = [0, 0, 37059702540, 359965498095, 416345917376, 53345994976, 0, 0] := by
  decide +kernel

theorem rows1965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1965 = true := by
  decide +kernel

theorem tot1965 : totK PD2M8K2 D2M8K2.t1965 = [0, 0, 197710604534, 475385928572, 200797830818, 9827254241, 0, 0] := by
  decide +kernel

theorem rows1966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1966 = true := by
  decide +kernel

theorem tot1966 : totK PD2M8K2 D2M8K2.t1966 = [0, 0, 193702581844, 472613384610, 205579275176, 12593797338, 0, 0] := by
  decide +kernel

theorem rows1967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1967 = true := by
  decide +kernel

theorem tot1967 : totK PD2M8K2 D2M8K2.t1967 = [0, 0, 164548234905, 478313567906, 247216653536, 11572547963, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
