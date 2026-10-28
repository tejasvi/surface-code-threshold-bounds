import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15444 = true := by
  decide +kernel

theorem tot15444 : totK PD2M8K2 D2M8K2.t15444 = [0, 193661760413, 461465414520, 242558884573, 23259966184, 0, 0, 0] := by
  decide +kernel

theorem rows15445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15445 = true := by
  decide +kernel

theorem tot15445 : totK PD2M8K2 D2M8K2.t15445 = [0, 155365546180, 465312030395, 258391033771, 13620119383, 0, 0, 0] := by
  decide +kernel

theorem rows15446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15446 = true := by
  decide +kernel

theorem tot15446 : totK PD2M8K2 D2M8K2.t15446 = [0, 0, 262928347998, 493787103339, 134685698941, 6978781128, 0, 0] := by
  decide +kernel

theorem rows15447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15447 = true := by
  decide +kernel

theorem tot15447 : totK PD2M8K2 D2M8K2.t15447 = [0, 67163829148, 314683561416, 388667987492, 108755839400, 4906626486, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
