import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8796 = true := by
  decide +kernel

theorem tot8796 : totK PD2M8K2 D2M8K2.t8796 = [0, 0, 165274986102, 481561915471, 237735144539, 12443528988, 0, 0] := by
  decide +kernel

theorem rows8797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8797 = true := by
  decide +kernel

theorem tot8797 : totK PD2M8K2 D2M8K2.t8797 = [0, 0, 169950936826, 457882399542, 244345629199, 17142859432, 0, 0] := by
  decide +kernel

theorem rows8798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8798 = true := by
  decide +kernel

theorem tot8798 : totK PD2M8K2 D2M8K2.t8798 = [0, 0, 186419938995, 448834453272, 219284943652, 16702988424, 0, 0] := by
  decide +kernel

theorem rows8799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8799 = true := by
  decide +kernel

theorem tot8799 : totK PD2M8K2 D2M8K2.t8799 = [0, 0, 75082883077, 417249583273, 355362863529, 33570998187, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
