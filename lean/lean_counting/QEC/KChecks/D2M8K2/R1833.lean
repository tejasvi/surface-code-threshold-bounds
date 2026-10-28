import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7332 = true := by
  decide +kernel

theorem tot7332 : totK PD2M8K2 D2M8K2.t7332 = [0, 0, 0, 272315241946, 499484425574, 130710853924, 4009909289, 0] := by
  decide +kernel

theorem rows7333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7333 = true := by
  decide +kernel

theorem tot7333 : totK PD2M8K2 D2M8K2.t7333 = [0, 0, 141127144203, 387546271424, 304604155666, 73930543791, 1149959346, 0] := by
  decide +kernel

theorem rows7334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7334 = true := by
  decide +kernel

theorem tot7334 : totK PD2M8K2 D2M8K2.t7334 = [0, 0, 175258362267, 440024989521, 264299579778, 18380431988, 0, 0] := by
  decide +kernel

theorem rows7335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7335 = true := by
  decide +kernel

theorem tot7335 : totK PD2M8K2 D2M8K2.t7335 = [0, 0, 86061661429, 422136687345, 364228470527, 35512186398, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
