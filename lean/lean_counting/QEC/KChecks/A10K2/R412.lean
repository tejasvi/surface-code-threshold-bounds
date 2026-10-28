import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1648 = true := by
  decide +kernel

theorem tot1648 : totK PA10K2 A10K2.t1648 = [0, 0, 150212182865, 843850371182, 1867294332636, 1451569905686, 301733138464, 10589884120, 0, 0] := by
  decide +kernel

theorem rows1649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1649 = true := by
  decide +kernel

theorem tot1649 : totK PA10K2 A10K2.t1649 = [0, 0, 519371241658, 1847379652647, 1863530467682, 514037375900, 31608797364, 0, 0, 0] := by
  decide +kernel

theorem rows1650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1650 = true := by
  decide +kernel

theorem tot1650 : totK PA10K2 A10K2.t1650 = [0, 0, 110080449477, 1291508799309, 2336571222579, 904918632612, 65326404304, 0, 0, 0] := by
  decide +kernel

theorem rows1651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1651 = true := by
  decide +kernel

theorem tot1651 : totK PA10K2 A10K2.t1651 = [0, 0, 424342525602, 1461768173286, 1838489903177, 916267788613, 153851967938, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
