import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6716 = true := by
  decide +kernel

theorem tot6716 : totK PD2M8K2 D2M8K2.t6716 = [0, 0, 92057834958, 407317927455, 336905066882, 35347784302, 0, 0] := by
  decide +kernel

theorem rows6717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6717 = true := by
  decide +kernel

theorem tot6717 : totK PD2M8K2 D2M8K2.t6717 = [0, 0, 213311412392, 477005164996, 186754773108, 10035653310, 0, 0] := by
  decide +kernel

theorem rows6718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6718 = true := by
  decide +kernel

theorem tot6718 : totK PD2M8K2 D2M8K2.t6718 = [0, 0, 220047926638, 497381006233, 166356740450, 2954213869, 0, 0] := by
  decide +kernel

theorem rows6719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6719 = true := by
  decide +kernel

theorem tot6719 : totK PD2M8K2 D2M8K2.t6719 = [0, 0, 181828281313, 464466798467, 219454015265, 17982963062, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
