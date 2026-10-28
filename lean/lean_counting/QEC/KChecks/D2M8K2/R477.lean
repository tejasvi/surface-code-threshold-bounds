import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1908 = true := by
  decide +kernel

theorem tot1908 : totK PD2M8K2 D2M8K2.t1908 = [0, 88989031395, 380015099581, 362725506653, 64490199880, 1369150432, 0, 0] := by
  decide +kernel

theorem rows1909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1909 = true := by
  decide +kernel

theorem tot1909 : totK PD2M8K2 D2M8K2.t1909 = [0, 0, 298527406118, 514116795505, 85626887428, 0, 0, 0] := by
  decide +kernel

theorem rows1910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1910 = true := by
  decide +kernel

theorem tot1910 : totK PD2M8K2 D2M8K2.t1910 = [0, 178211267531, 443952355064, 269432147040, 30298768840, 0, 0, 0] := by
  decide +kernel

theorem rows1911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1911 = true := by
  decide +kernel

theorem tot1911 : totK PD2M8K2 D2M8K2.t1911 = [0, 210064609513, 469344364567, 216700075673, 15493458204, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
