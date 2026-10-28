import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7864 = true := by
  decide +kernel

theorem tot7864 : totK PD2M8K2 D2M8K2.t7864 = [0, 89240473698, 355924474944, 376825327374, 82841695646, 1268739303, 0, 0] := by
  decide +kernel

theorem rows7865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7865 = true := by
  decide +kernel

theorem tot7865 : totK PD2M8K2 D2M8K2.t7865 = [0, 0, 224945311562, 502080141826, 166946474301, 4927173082, 0, 0] := by
  decide +kernel

theorem rows7866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7866 = true := by
  decide +kernel

theorem tot7866 : totK PD2M8K2 D2M8K2.t7866 = [0, 0, 177538341811, 465150479940, 233688781979, 16132694755, 0, 0] := by
  decide +kernel

theorem rows7867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7867 = true := by
  decide +kernel

theorem tot7867 : totK PD2M8K2 D2M8K2.t7867 = [0, 0, 208562335790, 469691465375, 172602753199, 6440832183, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
