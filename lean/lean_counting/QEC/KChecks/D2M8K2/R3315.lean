import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13260 = true := by
  decide +kernel

theorem tot13260 : totK PD2M8K2 D2M8K2.t13260 = [0, 160882570615, 418048861018, 269332454698, 60190896860, 2566665356, 0, 0] := by
  decide +kernel

theorem rows13261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13261 = true := by
  decide +kernel

theorem tot13261 : totK PD2M8K2 D2M8K2.t13261 = [0, 172659237846, 433947785873, 272773617186, 30498142501, 0, 0, 0] := by
  decide +kernel

theorem rows13262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13262 = true := by
  decide +kernel

theorem tot13262 : totK PD2M8K2 D2M8K2.t13262 = [0, 91681601894, 381894913438, 352030858114, 58219738598, 1096156699, 0, 0] := by
  decide +kernel

theorem rows13263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13263 = true := by
  decide +kernel

theorem tot13263 : totK PD2M8K2 D2M8K2.t13263 = [0, 0, 332924862436, 515490806703, 79671989942, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
