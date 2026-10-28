import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2808 = true := by
  decide +kernel

theorem tot2808 : totK PD2M8K2 D2M8K2.t2808 = [0, 281340180806, 498664691332, 117860483611, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows2809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2809 = true := by
  decide +kernel

theorem tot2809 : totK PD2M8K2 D2M8K2.t2809 = [0, 192263304036, 473478912560, 205866271513, 8669917095, 0, 0, 0] := by
  decide +kernel

theorem rows2810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2810 = true := by
  decide +kernel

theorem tot2810 : totK PD2M8K2 D2M8K2.t2810 = [0, 178724165861, 474594498820, 223222334694, 14632507742, 0, 0, 0] := by
  decide +kernel

theorem rows2811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2811 = true := by
  decide +kernel

theorem tot2811 : totK PD2M8K2 D2M8K2.t2811 = [0, 163023405172, 438354508080, 232777619681, 19294676230, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
