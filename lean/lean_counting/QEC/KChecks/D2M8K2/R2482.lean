import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9928 = true := by
  decide +kernel

theorem tot9928 : totK PD2M8K2 D2M8K2.t9928 = [0, 0, 195299690170, 460641647306, 235134464180, 14233002195, 0, 0] := by
  decide +kernel

theorem rows9929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9929 = true := by
  decide +kernel

theorem tot9929 : totK PD2M8K2 D2M8K2.t9929 = [0, 0, 187892713463, 458314307951, 209477330289, 12373752831, 0, 0] := by
  decide +kernel

theorem rows9930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9930 = true := by
  decide +kernel

theorem tot9930 : totK PD2M8K2 D2M8K2.t9930 = [0, 0, 7870389106, 316210551844, 484296102758, 77513296146, 1164319620, 0] := by
  decide +kernel

theorem rows9931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9931 = true := by
  decide +kernel

theorem tot9931 : totK PD2M8K2 D2M8K2.t9931 = [0, 0, 103574659592, 419764161835, 344584411206, 32440800917, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
