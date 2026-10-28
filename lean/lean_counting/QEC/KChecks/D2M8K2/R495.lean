import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1980 = true := by
  decide +kernel

theorem tot1980 : totK PD2M8K2 D2M8K2.t1980 = [0, 87085179265, 341130267989, 384733286608, 85530562405, 1197396724, 0, 0] := by
  decide +kernel

theorem rows1981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1981 = true := by
  decide +kernel

theorem tot1981 : totK PD2M8K2 D2M8K2.t1981 = [0, 0, 220490582015, 483142238357, 168827898831, 9473607896, 0, 0] := by
  decide +kernel

theorem rows1982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1982 = true := by
  decide +kernel

theorem tot1982 : totK PD2M8K2 D2M8K2.t1982 = [0, 155221297835, 415461208446, 269954644180, 58573789801, 2566665356, 0, 0] := by
  decide +kernel

theorem rows1983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1983 = true := by
  decide +kernel

theorem tot1983 : totK PD2M8K2 D2M8K2.t1983 = [0, 154666946550, 432359356006, 282821990483, 31597866779, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
