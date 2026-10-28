import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5708 = true := by
  decide +kernel

theorem tot5708 : totK PA10K2 A10K2.t5708 = [0, 0, 573994530211, 1949407522450, 1883498704586, 479971200712, 18381869251, 0, 0, 0] := by
  decide +kernel

theorem rows5709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5709 = true := by
  decide +kernel

theorem tot5709 : totK PA10K2 A10K2.t5709 = [0, 0, 461108409457, 1857698630554, 1903047004007, 449755996915, 25667075836, 0, 0, 0] := by
  decide +kernel

theorem rows5710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5710 = true := by
  decide +kernel

theorem tot5710 : totK PA10K2 A10K2.t5710 = [0, 0, 219095777392, 1099997965934, 1962997990828, 1130854628597, 211980913377, 20060612110, 0, 0] := by
  decide +kernel

theorem rows5711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5711 = true := by
  decide +kernel

theorem tot5711 : totK PA10K2 A10K2.t5711 = [0, 0, 174394568313, 857987376312, 1835558933975, 1391050166537, 285573455041, 10589884120, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
