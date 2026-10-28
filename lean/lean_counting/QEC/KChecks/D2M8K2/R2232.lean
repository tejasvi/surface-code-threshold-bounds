import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8928 = true := by
  decide +kernel

theorem tot8928 : totK PD2M8K2 D2M8K2.t8928 = [0, 157598256158, 475301262312, 240679470781, 11083510705, 0, 0, 0] := by
  decide +kernel

theorem rows8929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8929 = true := by
  decide +kernel

theorem tot8929 : totK PD2M8K2 D2M8K2.t8929 = [0, 166995070911, 461070780178, 239573024487, 14052954032, 0, 0, 0] := by
  decide +kernel

theorem rows8930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8930 = true := by
  decide +kernel

theorem tot8930 : totK PD2M8K2 D2M8K2.t8930 = [0, 0, 285754154796, 477702327835, 86160447772, 1239866073, 0, 0] := by
  decide +kernel

theorem rows8931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8931 = true := by
  decide +kernel

theorem tot8931 : totK PD2M8K2 D2M8K2.t8931 = [0, 162011809405, 429071692115, 304358549685, 33946028556, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
