import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14928 = true := by
  decide +kernel

theorem tot14928 : totK PD2M8K2 D2M8K2.t14928 = [0, 179867083042, 463953747280, 250331884931, 14034744956, 0, 0, 0] := by
  decide +kernel

theorem rows14929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14929 = true := by
  decide +kernel

theorem tot14929 : totK PD2M8K2 D2M8K2.t14929 = [0, 0, 266122981586, 504761714838, 126174295720, 1268739303, 0, 0] := by
  decide +kernel

theorem rows14930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14930 = true := by
  decide +kernel

theorem tot14930 : totK PD2M8K2 D2M8K2.t14930 = [0, 0, 178461155434, 478817253288, 206573671017, 8537527025, 0, 0] := by
  decide +kernel

theorem rows14931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14931 = true := by
  decide +kernel

theorem tot14931 : totK PD2M8K2 D2M8K2.t14931 = [0, 0, 178586387761, 463931734573, 222761599790, 17453112854, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
