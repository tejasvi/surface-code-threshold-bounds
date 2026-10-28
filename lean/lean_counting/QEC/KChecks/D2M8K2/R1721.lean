import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6884 = true := by
  decide +kernel

theorem tot6884 : totK PD2M8K2 D2M8K2.t6884 = [0, 152755471415, 455642616431, 256804355566, 15970643435, 0, 0, 0] := by
  decide +kernel

theorem rows6885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6885 = true := by
  decide +kernel

theorem tot6885 : totK PD2M8K2 D2M8K2.t6885 = [0, 0, 269430022399, 493937019907, 87662903114, 1310285577, 0, 0] := by
  decide +kernel

theorem rows6886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6886 = true := by
  decide +kernel

theorem tot6886 : totK PD2M8K2 D2M8K2.t6886 = [0, 145231957340, 405286763868, 336890455698, 41495259161, 0, 0, 0] := by
  decide +kernel

theorem rows6887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6887 = true := by
  decide +kernel

theorem tot6887 : totK PD2M8K2 D2M8K2.t6887 = [0, 187523879549, 458694857523, 231704918381, 13129461788, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
