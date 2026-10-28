import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14776 = true := by
  decide +kernel

theorem tot14776 : totK PD2M8K2 D2M8K2.t14776 = [186770637862, 463182314039, 233238594760, 16784765355, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14777 = true := by
  decide +kernel

theorem tot14777 : totK PD2M8K2 D2M8K2.t14777 = [0, 358966688034, 497405964352, 68851325175, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14778 = true := by
  decide +kernel

theorem tot14778 : totK PD2M8K2 D2M8K2.t14778 = [162555694144, 399115534688, 279562366938, 71932660812, 2739859532, 0, 0, 0] := by
  decide +kernel

theorem rows14779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14779 = true := by
  decide +kernel

theorem tot14779 : totK PD2M8K2 D2M8K2.t14779 = [174172422443, 444727256189, 266648332390, 20881433857, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
