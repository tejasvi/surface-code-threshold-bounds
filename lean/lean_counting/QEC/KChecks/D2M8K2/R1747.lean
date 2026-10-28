import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6988 = true := by
  decide +kernel

theorem tot6988 : totK PD2M8K2 D2M8K2.t6988 = [0, 157265978880, 491358360413, 250004930653, 13988764034, 0, 0, 0] := by
  decide +kernel

theorem rows6989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6989 = true := by
  decide +kernel

theorem tot6989 : totK PD2M8K2 D2M8K2.t6989 = [0, 88459214294, 320374858555, 358534081220, 129472715211, 13959483670, 0, 0] := by
  decide +kernel

theorem rows6990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6990 = true := by
  decide +kernel

theorem tot6990 : totK PD2M8K2 D2M8K2.t6990 = [0, 0, 190692616444, 472162046353, 228289966227, 10772333413, 0, 0] := by
  decide +kernel

theorem rows6991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6991 = true := by
  decide +kernel

theorem tot6991 : totK PD2M8K2 D2M8K2.t6991 = [0, 84183811908, 261765488050, 370382194561, 167678970663, 8073768252, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
