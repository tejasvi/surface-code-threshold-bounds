import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1632 = true := by
  decide +kernel

theorem tot1632 : totK PA10K2 A10K2.t1632 = [0, 0, 0, 1042245256554, 2430957960834, 1085975355834, 86036279316, 0, 0, 0] := by
  decide +kernel

theorem rows1633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1633 = true := by
  decide +kernel

theorem tot1633 : totK PA10K2 A10K2.t1633 = [0, 0, 0, 522334884169, 1945590940412, 1822259736065, 377530200860, 11740475125, 0, 0] := by
  decide +kernel

theorem rows1634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1634 = true := by
  decide +kernel

theorem tot1634 : totK PA10K2 A10K2.t1634 = [0, 0, 0, 487170417309, 1834903299222, 1891395609100, 449841533965, 32239129156, 0, 0] := by
  decide +kernel

theorem rows1635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1635 = true := by
  decide +kernel

theorem tot1635 : totK PA10K2 A10K2.t1635 = [0, 0, 0, 649485465986, 2137107318704, 1683279368440, 259672945146, 6239800209, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
