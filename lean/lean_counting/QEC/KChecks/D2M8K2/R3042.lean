import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12168 = true := by
  decide +kernel

theorem tot12168 : totK PD2M8K2 D2M8K2.t12168 = [92075173518, 138168098488, 111624729539, 332797294418, 202277596553, 17080783126, 0, 0] := by
  decide +kernel

theorem rows12169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12169 = true := by
  decide +kernel

theorem tot12169 : totK PD2M8K2 D2M8K2.t12169 = [173924699396, 478225351535, 236512428690, 11038245751, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12170 = true := by
  decide +kernel

theorem tot12170 : totK PD2M8K2 D2M8K2.t12170 = [169294685987, 460650973848, 248462579857, 15248594464, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12171 = true := by
  decide +kernel

theorem tot12171 : totK PD2M8K2 D2M8K2.t12171 = [0, 273860939126, 507487512732, 113637923127, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
