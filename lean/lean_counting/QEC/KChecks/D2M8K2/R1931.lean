import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7724 = true := by
  decide +kernel

theorem tot7724 : totK PD2M8K2 D2M8K2.t7724 = [0, 0, 0, 126525245439, 443496997351, 289837462942, 20940863810, 0] := by
  decide +kernel

theorem rows7725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7725 = true := by
  decide +kernel

theorem tot7725 : totK PD2M8K2 D2M8K2.t7725 = [0, 0, 0, 0, 217867420468, 467225935924, 173647507926, 9579374723] := by
  decide +kernel

theorem rows7726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7726 = true := by
  decide +kernel

theorem tot7726 : totK PD2M8K2 D2M8K2.t7726 = [0, 0, 0, 82638451573, 329946039744, 335572237316, 87857138610, 3436822651] := by
  decide +kernel

theorem rows7727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7727 = true := by
  decide +kernel

theorem tot7727 : totK PD2M8K2 D2M8K2.t7727 = [0, 0, 0, 180220183105, 459305210181, 237008754445, 18101699538, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
