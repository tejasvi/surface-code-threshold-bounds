import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7856 = true := by
  decide +kernel

theorem tot7856 : totK PD2M8K2 D2M8K2.t7856 = [0, 136429283381, 447570426711, 300762170273, 23361826984, 0, 0, 0] := by
  decide +kernel

theorem rows7857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7857 = true := by
  decide +kernel

theorem tot7857 : totK PD2M8K2 D2M8K2.t7857 = [0, 0, 205550013132, 494195719889, 183913875566, 9587713104, 0, 0] := by
  decide +kernel

theorem rows7858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7858 = true := by
  decide +kernel

theorem tot7858 : totK PD2M8K2 D2M8K2.t7858 = [0, 84547450418, 319303972593, 379636345990, 101370636056, 3462014130, 0, 0] := by
  decide +kernel

theorem rows7859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7859 = true := by
  decide +kernel

theorem tot7859 : totK PD2M8K2 D2M8K2.t7859 = [0, 176853009588, 459309913139, 261114197431, 22925453131, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
