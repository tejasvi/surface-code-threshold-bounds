import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5740 = true := by
  decide +kernel

theorem tot5740 : totK PA10K2 A10K2.t5740 = [0, 0, 543336503273, 1960183711234, 1875897483966, 404005299321, 13227942247, 0, 0, 0] := by
  decide +kernel

theorem rows5741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5741 = true := by
  decide +kernel

theorem tot5741 : totK PA10K2 A10K2.t5741 = [0, 0, 466555047417, 1671892832166, 1913022028272, 589635262606, 50267370225, 0, 0, 0] := by
  decide +kernel

theorem rows5742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5742 = true := by
  decide +kernel

theorem tot5742 : totK PA10K2 A10K2.t5742 = [0, 0, 112574319960, 1285093293190, 2309063030755, 906331870204, 72317855408, 0, 0, 0] := by
  decide +kernel

theorem rows5743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5743 = true := by
  decide +kernel

theorem tot5743 : totK PA10K2 A10K2.t5743 = [0, 0, 310366196018, 1239171114444, 1871385507338, 1049686861010, 208228404469, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
