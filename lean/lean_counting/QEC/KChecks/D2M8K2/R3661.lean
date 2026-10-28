import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14644 = true := by
  decide +kernel

theorem tot14644 : totK PD2M8K2 D2M8K2.t14644 = [0, 175568789627, 452380375923, 268990746639, 28520985951, 0, 0, 0] := by
  decide +kernel

theorem rows14645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14645 = true := by
  decide +kernel

theorem tot14645 : totK PD2M8K2 D2M8K2.t14645 = [0, 111257890084, 421682914167, 340588285797, 31903461104, 0, 0, 0] := by
  decide +kernel

theorem rows14646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14646 = true := by
  decide +kernel

theorem tot14646 : totK PD2M8K2 D2M8K2.t14646 = [0, 0, 234615427263, 501398614792, 161215794143, 2516391818, 0, 0] := by
  decide +kernel

theorem rows14647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14647 = true := by
  decide +kernel

theorem tot14647 : totK PD2M8K2 D2M8K2.t14647 = [0, 71689983455, 223987417104, 368168293677, 200991729431, 15310102822, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
