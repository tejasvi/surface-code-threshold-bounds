import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2836 = true := by
  decide +kernel

theorem tot2836 : totK PD2M8K2 D2M8K2.t2836 = [66777847114, 315263835969, 400972009561, 107086356301, 3880716147, 0, 0, 0] := by
  decide +kernel

theorem rows2837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2837 = true := by
  decide +kernel

theorem tot2837 : totK PD2M8K2 D2M8K2.t2837 = [177731433298, 454805235034, 268615586842, 27945535849, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2838 = true := by
  decide +kernel

theorem tot2838 : totK PD2M8K2 D2M8K2.t2838 = [172965736300, 468410438019, 259731136320, 16021040295, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2839 = true := by
  decide +kernel

theorem tot2839 : totK PD2M8K2 D2M8K2.t2839 = [0, 243371491860, 501704505309, 145468255239, 2300468944, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
