import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2560 = true := by
  decide +kernel

theorem tot2560 : totK PD2M8K2 D2M8K2.t2560 = [51549331234, 228051010299, 406364697857, 176967287276, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows2561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2561 = true := by
  decide +kernel

theorem tot2561 : totK PD2M8K2 D2M8K2.t2561 = [183588479806, 465628716222, 245424395373, 23250197218, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2562 = true := by
  decide +kernel

theorem tot2562 : totK PD2M8K2 D2M8K2.t2562 = [174512448385, 465592112620, 244942656461, 13593906775, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2563 = true := by
  decide +kernel

theorem tot2563 : totK PD2M8K2 D2M8K2.t2563 = [0, 286764389576, 488650961978, 113270103107, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
