import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2964 = true := by
  decide +kernel

theorem tot2964 : totK PD2M8K2 D2M8K2.t2964 = [0, 195011001131, 476968162500, 225826173371, 12387829827, 0, 0, 0] := by
  decide +kernel

theorem rows2965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2965 = true := by
  decide +kernel

theorem tot2965 : totK PD2M8K2 D2M8K2.t2965 = [0, 56604719061, 330714903349, 407355128214, 88923295042, 1242138600, 0, 0] := by
  decide +kernel

theorem rows2966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2966 = true := by
  decide +kernel

theorem tot2966 : totK PD2M8K2 D2M8K2.t2966 = [0, 0, 217533666563, 469360370661, 163821046214, 7182288656, 0, 0] := by
  decide +kernel

theorem rows2967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2967 = true := by
  decide +kernel

theorem tot2967 : totK PD2M8K2 D2M8K2.t2967 = [0, 120208286280, 339512638693, 296553579652, 130097997909, 13326740810, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
