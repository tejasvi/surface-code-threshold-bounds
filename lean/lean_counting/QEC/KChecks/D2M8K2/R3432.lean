import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13728 = true := by
  decide +kernel

theorem tot13728 : totK PD2M8K2 D2M8K2.t13728 = [0, 50849869571, 245073651634, 438250352107, 158504161829, 5348807592, 0, 0] := by
  decide +kernel

theorem rows13729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13729 = true := by
  decide +kernel

theorem tot13729 : totK PD2M8K2 D2M8K2.t13729 = [0, 194840931100, 465044149220, 243705489388, 20524214372, 0, 0, 0] := by
  decide +kernel

theorem rows13730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13730 = true := by
  decide +kernel

theorem tot13730 : totK PD2M8K2 D2M8K2.t13730 = [0, 191642939225, 469626647348, 223690769407, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows13731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13731 = true := by
  decide +kernel

theorem tot13731 : totK PD2M8K2 D2M8K2.t13731 = [0, 0, 303846693272, 493489175063, 97787519145, 1178750802, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
