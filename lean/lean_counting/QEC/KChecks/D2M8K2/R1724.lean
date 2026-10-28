import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6896 = true := by
  decide +kernel

theorem tot6896 : totK PD2M8K2 D2M8K2.t6896 = [0, 176428586533, 463107113554, 253764272541, 27563437163, 0, 0, 0] := by
  decide +kernel

theorem rows6897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6897 = true := by
  decide +kernel

theorem tot6897 : totK PD2M8K2 D2M8K2.t6897 = [0, 175371570310, 453741099782, 258827622919, 18423607359, 0, 0, 0] := by
  decide +kernel

theorem rows6898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6898 = true := by
  decide +kernel

theorem tot6898 : totK PD2M8K2 D2M8K2.t6898 = [0, 93669046305, 349688274067, 370402782081, 74058332404, 1242138600, 0, 0] := by
  decide +kernel

theorem rows6899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6899 = true := by
  decide +kernel

theorem tot6899 : totK PD2M8K2 D2M8K2.t6899 = [0, 0, 259228398531, 477468575114, 137770353253, 4600645648, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
