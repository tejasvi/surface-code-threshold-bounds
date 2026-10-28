import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13748 = true := by
  decide +kernel

theorem tot13748 : totK PD2M8K2 D2M8K2.t13748 = [0, 118700538460, 355523441629, 328739548048, 76387844648, 3462014130, 0, 0] := by
  decide +kernel

theorem rows13749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13749 = true := by
  decide +kernel

theorem tot13749 : totK PD2M8K2 D2M8K2.t13749 = [0, 171233314097, 447760189922, 256696764441, 25689840162, 0, 0, 0] := by
  decide +kernel

theorem rows13750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13750 = true := by
  decide +kernel

theorem tot13750 : totK PD2M8K2 D2M8K2.t13750 = [0, 102219663118, 402780482019, 329920625116, 50814880096, 1198073392, 0, 0] := by
  decide +kernel

theorem rows13751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13751 = true := by
  decide +kernel

theorem tot13751 : totK PD2M8K2 D2M8K2.t13751 = [0, 0, 231904120975, 488778116430, 152463572700, 8404294179, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
