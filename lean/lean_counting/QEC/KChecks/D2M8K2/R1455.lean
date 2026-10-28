import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5820 = true := by
  decide +kernel

theorem tot5820 : totK PD2M8K2 D2M8K2.t5820 = [166181834610, 465826590063, 252547990231, 15130884434, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5821 = true := by
  decide +kernel

theorem tot5821 : totK PD2M8K2 D2M8K2.t5821 = [0, 280844826273, 499943061375, 113261153141, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows5822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5822 = true := by
  decide +kernel

theorem tot5822 : totK PD2M8K2 D2M8K2.t5822 = [149847357467, 408807659441, 337534576565, 43375753268, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5823 = true := by
  decide +kernel

theorem tot5823 : totK PD2M8K2 D2M8K2.t5823 = [192476319716, 475172905570, 224291460743, 15089499746, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
