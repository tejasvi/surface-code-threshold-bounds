import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t864 = true := by
  decide +kernel

theorem tot864 : totK PD2M8K2 D2M8K2.t864 = [0, 0, 242183258383, 486622574525, 176489856006, 9871637500, 0, 0] := by
  decide +kernel

theorem rows865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t865 = true := by
  decide +kernel

theorem tot865 : totK PD2M8K2 D2M8K2.t865 = [0, 0, 218741539095, 486320858385, 184356711408, 6781982568, 0, 0] := by
  decide +kernel

theorem rows866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t866 = true := by
  decide +kernel

theorem tot866 : totK PD2M8K2 D2M8K2.t866 = [0, 0, 218098247213, 486055537615, 158108529828, 4703443217, 0, 0] := by
  decide +kernel

theorem rows867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t867 = true := by
  decide +kernel

theorem tot867 : totK PD2M8K2 D2M8K2.t867 = [0, 0, 187530743178, 484924106465, 188531370434, 9197669987, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
