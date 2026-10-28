import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14904 = true := by
  decide +kernel

theorem tot14904 : totK PD2M8K2 D2M8K2.t14904 = [0, 186498615018, 460693597046, 239053193484, 20859766089, 0, 0, 0] := by
  decide +kernel

theorem rows14905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14905 = true := by
  decide +kernel

theorem tot14905 : totK PD2M8K2 D2M8K2.t14905 = [0, 195807975989, 475466552869, 213395760000, 12050698813, 0, 0, 0] := by
  decide +kernel

theorem rows14906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14906 = true := by
  decide +kernel

theorem tot14906 : totK PD2M8K2 D2M8K2.t14906 = [0, 19498933008, 320339631995, 463313442262, 80245574095, 1107157161, 0, 0] := by
  decide +kernel

theorem rows14907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14907 = true := by
  decide +kernel

theorem tot14907 : totK PD2M8K2 D2M8K2.t14907 = [0, 86757284321, 314765188226, 368127597709, 101433185043, 3824247485, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
