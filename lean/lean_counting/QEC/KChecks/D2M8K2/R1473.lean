import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5892 = true := by
  decide +kernel

theorem tot5892 : totK PD2M8K2 D2M8K2.t5892 = [180245559322, 465904588035, 255947061719, 23041996261, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5893 = true := by
  decide +kernel

theorem tot5893 : totK PD2M8K2 D2M8K2.t5893 = [157398166429, 456194546908, 266439568158, 21991891729, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5894 = true := by
  decide +kernel

theorem tot5894 : totK PD2M8K2 D2M8K2.t5894 = [0, 241125287055, 508661529576, 141384202634, 2309606161, 0, 0, 0] := by
  decide +kernel

theorem rows5895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5895 = true := by
  decide +kernel

theorem tot5895 : totK PD2M8K2 D2M8K2.t5895 = [63578106465, 269836460749, 387996357770, 145736690203, 10740121073, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
