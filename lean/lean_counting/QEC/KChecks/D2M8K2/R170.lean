import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t680 = true := by
  decide +kernel

theorem tot680 : totK PD2M8K2 D2M8K2.t680 = [0, 193019863207, 479260852509, 220393213544, 12439805748, 0, 0, 0] := by
  decide +kernel

theorem rows681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t681 = true := by
  decide +kernel

theorem tot681 : totK PD2M8K2 D2M8K2.t681 = [0, 19434652667, 312400418790, 453498779649, 89199916630, 1171084559, 0, 0] := by
  decide +kernel

theorem rows682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t682 = true := by
  decide +kernel

theorem tot682 : totK PD2M8K2 D2M8K2.t682 = [0, 0, 199335089958, 455945902927, 187230465404, 11934365838, 0, 0] := by
  decide +kernel

theorem rows683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t683 = true := by
  decide +kernel

theorem tot683 : totK PD2M8K2 D2M8K2.t683 = [0, 169370488216, 460517735472, 249589799188, 18230746809, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
