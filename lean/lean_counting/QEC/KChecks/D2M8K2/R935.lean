import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3740 = true := by
  decide +kernel

theorem tot3740 : totK PD2M8K2 D2M8K2.t3740 = [0, 136878919973, 449760261359, 306705963722, 31261425716, 0, 0, 0] := by
  decide +kernel

theorem rows3741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3741 = true := by
  decide +kernel

theorem tot3741 : totK PD2M8K2 D2M8K2.t3741 = [0, 0, 177906918991, 445648306907, 250311177649, 25191558099, 0, 0] := by
  decide +kernel

theorem rows3742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3742 = true := by
  decide +kernel

theorem tot3742 : totK PD2M8K2 D2M8K2.t3742 = [0, 0, 200145716364, 503843227076, 184066397318, 5206224793, 0, 0] := by
  decide +kernel

theorem rows3743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3743 = true := by
  decide +kernel

theorem tot3743 : totK PD2M8K2 D2M8K2.t3743 = [0, 155842267669, 383303009387, 256719848533, 92328696366, 6524090962, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
