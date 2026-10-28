import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7556 = true := by
  decide +kernel

theorem tot7556 : totK PD2M8K2 D2M8K2.t7556 = [0, 0, 216953280460, 494478555393, 182164176389, 9587713104, 0, 0] := by
  decide +kernel

theorem rows7557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7557 = true := by
  decide +kernel

theorem tot7557 : totK PD2M8K2 D2M8K2.t7557 = [0, 84415941621, 324824979701, 372172783261, 96890878481, 3462014130, 0, 0] := by
  decide +kernel

theorem rows7558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7558 = true := by
  decide +kernel

theorem tot7558 : totK PD2M8K2 D2M8K2.t7558 = [0, 176912389090, 451464992546, 267036204594, 27790099378, 0, 0, 0] := by
  decide +kernel

theorem rows7559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7559 = true := by
  decide +kernel

theorem tot7559 : totK PD2M8K2 D2M8K2.t7559 = [0, 158155883827, 455443122682, 260316517124, 14131118458, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
