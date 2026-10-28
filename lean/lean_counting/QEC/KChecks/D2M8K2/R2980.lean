import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11920 = true := by
  decide +kernel

theorem tot11920 : totK PD2M8K2 D2M8K2.t11920 = [0, 159649504657, 471467535758, 256010463759, 14823345701, 0, 0, 0] := by
  decide +kernel

theorem rows11921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11921 = true := by
  decide +kernel

theorem tot11921 : totK PD2M8K2 D2M8K2.t11921 = [0, 0, 265552521085, 502953975295, 133709914915, 4009909289, 0, 0] := by
  decide +kernel

theorem rows11922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11922 = true := by
  decide +kernel

theorem tot11922 : totK PD2M8K2 D2M8K2.t11922 = [0, 152282097245, 383870396640, 297491294151, 66136793052, 1149959346, 0, 0] := by
  decide +kernel

theorem rows11923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11923 = true := by
  decide +kernel

theorem tot11923 : totK PD2M8K2 D2M8K2.t11923 = [0, 167036150836, 438480365528, 283727640092, 30435264497, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
