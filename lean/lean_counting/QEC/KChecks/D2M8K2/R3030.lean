import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12120 = true := by
  decide +kernel

theorem tot12120 : totK PD2M8K2 D2M8K2.t12120 = [0, 133653445399, 348097554039, 293447741525, 119766345733, 9043051330, 0, 0] := by
  decide +kernel

theorem rows12121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12121 = true := by
  decide +kernel

theorem tot12121 : totK PD2M8K2 D2M8K2.t12121 = [0, 185260757517, 450491186559, 228477709474, 17049611299, 0, 0, 0] := by
  decide +kernel

theorem rows12122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12122 = true := by
  decide +kernel

theorem tot12122 : totK PD2M8K2 D2M8K2.t12122 = [0, 84364237255, 387608535589, 339483796830, 58336334447, 1310517177, 0, 0] := by
  decide +kernel

theorem rows12123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12123 = true := by
  decide +kernel

theorem tot12123 : totK PD2M8K2 D2M8K2.t12123 = [0, 0, 308840694184, 513058128706, 68930050696, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
