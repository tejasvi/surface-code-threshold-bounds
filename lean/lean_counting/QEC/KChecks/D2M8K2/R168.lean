import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t672 = true := by
  decide +kernel

theorem tot672 : totK PD2M8K2 D2M8K2.t672 = [0, 180895693486, 474489240694, 221990509395, 11137111515, 0, 0, 0] := by
  decide +kernel

theorem rows673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t673 = true := by
  decide +kernel

theorem tot673 : totK PD2M8K2 D2M8K2.t673 = [0, 197368807610, 476518497481, 199509135649, 12126792705, 0, 0, 0] := by
  decide +kernel

theorem rows674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t674 = true := by
  decide +kernel

theorem tot674 : totK PD2M8K2 D2M8K2.t674 = [0, 191022862267, 466441789735, 211602301380, 12361325328, 0, 0, 0] := by
  decide +kernel

theorem rows675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t675 = true := by
  decide +kernel

theorem tot675 : totK PD2M8K2 D2M8K2.t675 = [0, 23343261889, 326338159218, 438547201962, 75369285992, 1239866073, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
