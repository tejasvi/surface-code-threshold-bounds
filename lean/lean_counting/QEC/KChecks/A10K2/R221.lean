import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t884 = true := by
  decide +kernel

theorem tot884 : totK PA10K2 A10K2.t884 = [451852813601, 1765612954258, 2002221117166, 606821169304, 43462649395, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t885 = true := by
  decide +kernel

theorem tot885 : totK PA10K2 A10K2.t885 = [332208314330, 1541239759417, 2170213880593, 907099037702, 76444601211, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t886 = true := by
  decide +kernel

theorem tot886 : totK PA10K2 A10K2.t886 = [0, 548159419531, 2009731497633, 2003459630073, 465176820863, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t887 = true := by
  decide +kernel

theorem tot887 : totK PA10K2 A10K2.t887 = [0, 418500826741, 1670114911808, 2042895869706, 756868134142, 69301444986, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
