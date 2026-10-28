import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1792 = true := by
  decide +kernel

theorem tot1792 : totK PD2M8K2 D2M8K2.t1792 = [0, 202087152119, 462531498560, 226083551897, 19649831279, 0, 0, 0] := by
  decide +kernel

theorem rows1793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1793 = true := by
  decide +kernel

theorem tot1793 : totK PD2M8K2 D2M8K2.t1793 = [0, 190574197763, 462182816481, 229773733202, 17007396831, 0, 0, 0] := by
  decide +kernel

theorem rows1794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1794 = true := by
  decide +kernel

theorem tot1794 : totK PD2M8K2 D2M8K2.t1794 = [0, 0, 292372926647, 490036655573, 111479196694, 1268739303, 0, 0] := by
  decide +kernel

theorem rows1795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1795 = true := by
  decide +kernel

theorem tot1795 : totK PD2M8K2 D2M8K2.t1795 = [0, 0, 202795023294, 477020928681, 184053405912, 7442000727, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
