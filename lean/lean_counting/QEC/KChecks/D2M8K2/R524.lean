import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2096 = true := by
  decide +kernel

theorem tot2096 : totK PD2M8K2 D2M8K2.t2096 = [0, 0, 161212847772, 460401196689, 271115991077, 20458103379, 0, 0] := by
  decide +kernel

theorem rows2097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2097 = true := by
  decide +kernel

theorem tot2097 : totK PD2M8K2 D2M8K2.t2097 = [0, 0, 217129280694, 478659657760, 203381743302, 8501583137, 0, 0] := by
  decide +kernel

theorem rows2098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2098 = true := by
  decide +kernel

theorem tot2098 : totK PD2M8K2 D2M8K2.t2098 = [0, 0, 177239970722, 479838459752, 233216086387, 13404039894, 0, 0] := by
  decide +kernel

theorem rows2099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2099 = true := by
  decide +kernel

theorem tot2099 : totK PD2M8K2 D2M8K2.t2099 = [0, 0, 178391653409, 454388506164, 253750919242, 16983577076, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
