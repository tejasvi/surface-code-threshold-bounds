import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1156 = true := by
  decide +kernel

theorem tot1156 : totK PA10K2 A10K2.t1156 = [0, 0, 280424296421, 1116408179620, 1858269016913, 1113838983815, 172237192518, 5546304973, 0, 0] := by
  decide +kernel

theorem rows1157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1157 = true := by
  decide +kernel

theorem tot1157 : totK PA10K2 A10K2.t1157 = [0, 0, 501003419019, 1993257326869, 2112351239106, 506464428491, 20094979411, 0, 0, 0] := by
  decide +kernel

theorem rows1158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1158 = true := by
  decide +kernel

theorem tot1158 : totK PA10K2 A10K2.t1158 = [0, 412976510926, 1341068214483, 1557883637471, 1114679535253, 494141032199, 48328894347, 0, 0, 0] := by
  decide +kernel

theorem rows1159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1159 = true := by
  decide +kernel

theorem tot1159 : totK PA10K2 A10K2.t1159 = [0, 388342531440, 1698260571693, 2083768672455, 711581025092, 49566425333, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
